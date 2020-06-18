#ifndef SOC_INTERRUPT_H
#define SOC_INTERRUPT_H


/**
** \brief List of IRQ numbers that can be registered by a userspace task
**
** used at init time, using sys_init() syscall.
** IRQ < 19 are denied, IRQ already managed by the kernel (e.g. the UART
** selected at config time) are denied.
** This list is a helper for the sys_init(REG_IRQ_HANDLER, ...) syscall.
*/
typedef enum {
    RTC_WKUP_IRQ = 19,
    FLASH_IRQ,
    RCC_IRQ,
    EXTI0_IRQ,
    EXTI1_IRQ,
    EXTI2_IRQ,
    EXTI3_IRQ,
    EXTI4_IRQ,
    DMA1_Stream0_IRQ,
    DMA1_Stream1_IRQ,
    DMA1_Stream2_IRQ,
    DMA1_Stream3_IRQ,
    DMA1_Stream4_IRQ,
    DMA1_Stream5_IRQ,
    DMA1_Stream6_IRQ,
    ADC_IRQ,
    CAN1_TX_IRQ,
    CAN1_RX0_IRQ,
    CAN1_RX1_IRQ,
    CAN1_SCE_IRQ,
    EXTI9_5_IRQ,
    TIM1_BRK_TIM9_IRQ,
    TIM1_UP_TIM10_IRQ,
    TIM1_TRG_COM_TIM11_IRQ,
    TIM1_CC_IRQ,
    TIM2_IRQ,
    TIM3_IRQ,
    TIM4_IRQ,
    I2C1_EV_IRQ,
    I2C1_ER_IRQ,
    I2C2_EV_IRQ,
    I2C2_ER_IRQ,
    SPI1_IRQ,
    SPI2_IRQ,
    USART1_IRQ,
    USART2_IRQ,
    USART3_IRQ,
    EXTI15_10_IRQ,
    RTC_Alarm_IRQ,
    OTG_FS_WKUP_IRQ,
    TIM8_BRK_TIM12_IRQ,
    TIM8_UP_TIM13_IRQ,
    TIM8_TRG_COM_TIM14_IRQ,
    TIM8_CC_IRQ,
    DMA1_Stream7_IRQ,
    FSMC_IRQ,
    SDIO_IRQ,
    TIM5_IRQ,
    SPI3_IRQ,
    UART4_IRQ,
    UART5_IRQ,
    TIM6_DAC_IRQ,
    TIM7_IRQ,
    DMA2_Stream0_IRQ,
    DMA2_Stream1_IRQ,
    DMA2_Stream2_IRQ,
    DMA2_Stream3_IRQ,
    DMA2_Stream4_IRQ,
    ETH_IRQ,
    ETH_WKUP_IRQ,
    CAN2_TX_IRQ,
    CAN2_RX0_IRQ,
    CAN2_RX1_IRQ,
    CAN2_SCE_IRQ,
    OTG_FS_IRQ,
    DMA2_Stream5_IRQ,
    DMA2_Stream6_IRQ,
    DMA2_Stream7_IRQ,
    USART6_IRQ,
    I2C3_EV_IRQ,
    I2C3_ER_IRQ,
    OTG_HS_EP1_OUT_IRQ,
    OTG_HS_EP1_IN_IRQ,
    OTG_HS_WKUP_IRQ,
    OTG_HS_IRQ,
    DCMI_IRQ,
    CRYP_IRQ,
    HASH_RNG_IRQ,
    FPU_IRQ,
} e_irq_id;

#endif/*!SOC_INTERRUPT_H*/
